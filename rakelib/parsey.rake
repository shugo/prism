# frozen_string_literal: true

# The parse.y backend's parser is generated from src/parsey/parse.y by lrama,
# the parser generator that CRuby itself uses. The generated src/parsey/parse.c
# is not checked in: the backend is an opt-in part of the build, and the only
# consumers of the generated parser are development checkouts (which have lrama
# through the Gemfile) and gem packaging (`rake build` generates it so that a
# `gem install prism -- --enable-parsey` does not need lrama). CRuby vendors
# lrama for its own parse.y, so a future --enable-prism-parsey build generates
# it the same way.

PARSEY_GRAMMAR = "src/parsey/parse.y"
PARSEY_SOURCE = "src/parsey/parse.c"

# lrama emits the token enum and the YYSTYPE union into a separate header, which
# the grammar's own prologue includes so that it can declare yylex() before the
# generated parser defines it. This mirrors how CRuby's parse.y is built.
PARSEY_HEADER = "src/parsey/parse.h"

# The grammar names its operator tokens the way CRuby's does, e.g.
#
#     %token tUPLUS RUBY_TOKEN(UPLUS) "unary+"
#
# which lrama cannot parse: RUBY_TOKEN is expanded to the token's number first,
# by a filter CRuby runs over the grammar on its way to the generator (see the
# .y.c rule in CRuby's common.mk). Both the filter and the table it reads the
# numbers out of are vendored here unmodified, so that the fork can keep
# spelling its tokens the way upstream does and so that the numbers have a
# single source. id2token.rb locates defs/id.def relative to itself, which is
# why the two sit next to each other in the same layout CRuby uses.
PARSEY_ID2TOKEN = "src/parsey/tool/id2token.rb"
PARSEY_IDDEF = "src/parsey/defs/id.def"

# Find lrama. Prefer an explicit LRAMA override, then the gem (which may be
# installed either as an executable or as a library), and finally a lrama
# checked out next to prism (CRuby vendors one in tool/lrama).
def parsey_lrama_command
  return ENV["LRAMA"] if ENV["LRAMA"]

  exe = ["lrama", "lrama.bat"].find { |name| ENV["PATH"].split(File::PATH_SEPARATOR).any? { |dir| File.executable?(File.join(dir, name)) } }
  return exe if exe

  # The bundle may carry the gem without exposing its executable on PATH
  # (bundler path installs, as CI uses).
  begin
    spec = Gem::Specification.find_by_name("lrama")
    return "#{Gem.ruby} #{File.join(spec.full_gem_path, spec.bindir, "lrama")}"
  rescue Gem::LoadError
  end

  vendored = File.expand_path("../../ruby/tool/lrama", __dir__)
  return "ruby -I#{vendored}/lib #{vendored}/exe/lrama" if File.exist?("#{vendored}/exe/lrama")

  nil
end

namespace :parsey do
  desc "Generate #{PARSEY_SOURCE} from #{PARSEY_GRAMMAR} using lrama"
  task :generate do
    lrama = parsey_lrama_command
    raise "lrama was not found. Install it with `gem install lrama`, or point LRAMA at it." if lrama.nil?

    id2token = File.expand_path(PARSEY_ID2TOKEN)

    # lrama derives the #include it emits for the header from the path it is
    # given, so run it from the grammar's own directory to get a bare
    # `#include "parse.h"`, and to keep the #line directives relative.
    #
    # The grammar is filtered through id2token.rb on the way in and reaches
    # lrama on stdin, which is why the file name is repeated after the `-`:
    # that is what lrama puts in the #line directives, and it needs to point at
    # the grammar rather than at the filter's output. CRuby invokes it the same
    # way.
    Dir.chdir(File.dirname(PARSEY_GRAMMAR)) do
      grammar = File.basename(PARSEY_GRAMMAR)
      # Two steps rather than a pipe: a pipe reports only the last command's
      # status, and lrama happily parses a truncated grammar into a broken
      # parser if the filter dies mid-stream.
      filtered = "#{grammar}.i"
      begin
        # -p repeats the filter's shebang flag: only CRuby re-reads flags
        # from a script's shebang, and without it JRuby runs the filter as
        # a no-op that silently emits an empty grammar.
        sh "ruby -p #{id2token} #{grammar} > #{filtered}"
        sh "#{lrama} -o#{File.basename(PARSEY_SOURCE)} -H#{File.basename(PARSEY_HEADER)} - #{grammar} < #{filtered}"
      ensure
        rm_f filtered
      end
    end
  end
end

# The backend itself is developed on the CRuby integration branch (ruby/ruby
# feature/prism-parsey), where a plain `make` regenerates the parser and the
# full CRuby test suite is at hand. These paths (CRuby name => fork name) are
# owned by that side and flow back here with parsey:sync_from_cruby; syncs in
# the other direction must leave them alone.
PARSEY_CRUBY_OWNED = {
  "prism/parsey" => "src/parsey",
  "test/prism/parsey" => "test/prism/parsey",
  "test/prism/parsey_equivalence_test.rb" => "test/prism/parsey_equivalence_test.rb",
  "test/prism/parsey_errors_test.rb" => "test/prism/parsey_errors_test.rb",
}

# CRuby path of a fork file under the gem sync mapping, or nil when the file
# has no synced counterpart (fork-only infrastructure, snapshots, extconf).
def parsey_cruby_counterpart(path)
  case path
  when "ext/prism/extconf.rb" then nil # CRuby keeps its own
  when %r{\Aext/prism/(.+)\z} then "prism/#{$1}"
  when %r{\Atest/prism/snapshots} then nil
  when %r{\A(lib/.+|test/prism/.+)\z} then $1
  when %r{\Asrc/(.+)\z} then "prism/#{$1}"
  when "include/prism.h" then "prism/prism.h"
  when %r{\Ainclude/prism/(.+)\z} then "prism/#{$1}"
  when "config.yml" then "prism/config.yml"
  when "prism.gemspec" then "lib/prism/prism.gemspec"
  when %r{\Atemplates/(.+)\z} then "prism/templates/#{$1}"
  end
end

namespace :parsey do
  desc "Sync the CRuby-owned backend paths from a ruby/ruby checkout"
  task :sync_from_cruby, [:cruby] do |_t, args|
    require "set"
    require "tmpdir"

    cruby = args[:cruby] || ENV["CRUBY"]
    # .git is a file in a linked worktree, so do not require a directory.
    unless cruby && File.exist?(File.join(cruby, ".git"))
      raise "usage: rake \"parsey:sync_from_cruby[/path/to/ruby]\" (or set CRUBY)"
    end

    fork_paths = PARSEY_CRUBY_OWNED.values
    cruby_paths = PARSEY_CRUBY_OWNED.keys

    # Refuse to clobber backend commits made here since the last sync: those
    # changes belong on the CRuby side. The sync commits carry a
    # `cruby-commit:` marker recording the CRuby commit they took.
    previous = nil
    last_sync = `git log -1 --grep='^cruby-commit:' --format=%H`.strip
    if last_sync.empty?
      puts "No previous sync commit found; skipping the divergence check."
    else
      previous = `git log -1 --format=%B #{last_sync}`[/^cruby-commit: (\h+)/, 1]
      stray = `git log --oneline #{last_sync}..HEAD -- #{fork_paths.join(" ")}`
      unless stray.empty? || ENV["FORCE"] == "1"
        abort "CRuby-owned paths have fork-side commits since the last sync" \
              " (FORCE=1 overrides):\n#{stray}"
      end
    end

    # Sync from HEAD, not the working tree, so the commit recorded in the
    # marker is the state actually taken.
    dirty = `git -C #{cruby} status --porcelain -- #{cruby_paths.join(" ")}`
    unless dirty.empty?
      abort "#{cruby} has uncommitted changes under the synced paths;" \
            " commit them first:\n#{dirty}"
    end

    head = `git -C #{cruby} rev-parse HEAD`.strip
    Dir.mktmpdir do |tmp|
      sh "git -C #{cruby} archive HEAD -- #{cruby_paths.join(" ")} | tar -x -C #{tmp}"
      # Delete-and-copy so that files removed on the CRuby side disappear;
      # ignored files (the generated parser) are left in place.
      `git ls-files -z -- #{fork_paths.join(" ")}`.split("\0").each { |file| rm_f file }
      PARSEY_CRUBY_OWNED.each do |from, to|
        from = File.join(tmp, from)
        next unless File.exist?(from)

        if File.directory?(from)
          mkdir_p to
          cp_r File.join(from, "."), to
        else
          cp from, to
        end
      end
    end

    changed = `git status --porcelain -- #{fork_paths.join(" ")}`
    if changed.empty?
      puts "Already in sync with ruby/ruby #{head}."
    else
      range = previous ? "#{previous[0, 10]}..#{head[0, 10]}" : head[0, 10]
      taken = previous ? `git -C #{cruby} log --oneline #{previous}..#{head} -- #{cruby_paths.join(" ")}` : ""
      puts changed
      body = taken.lines.map { |line| "* #{line}" }.join
      body << "\n" unless body.empty?
      puts <<~MESSAGE

        Synced ruby/ruby #{range}. Suggested commit message:

        Sync parsey from ruby/ruby #{head[0, 10]}

        #{body}cruby-commit: #{head}
      MESSAGE
    end

    # Shared files flow between the trees too, but by hand and in whichever
    # direction fits the change; report any that have drifted apart.
    tracked = `git -C #{cruby} ls-files -z`.split("\0").to_set
    drifted = `git ls-files -z`.split("\0").filter_map do |path|
      next if fork_paths.any? { |owned| path == owned || path.start_with?("#{owned}/") }

      counterpart = parsey_cruby_counterpart(path)
      next unless counterpart && tracked.include?(counterpart)

      "#{path} <> #{counterpart}" unless FileUtils.compare_file(path, File.join(cruby, counterpart))
    end
    unless drifted.empty?
      puts "\nShared files differing from the CRuby checkout (port by hand):"
      drifted.each { |pair| puts "  #{pair}" }
    end
  end
end

file PARSEY_SOURCE => [PARSEY_GRAMMAR, PARSEY_IDDEF, PARSEY_ID2TOKEN] do
  Rake::Task["parsey:generate"].invoke
end

file PARSEY_HEADER => PARSEY_SOURCE

# The compile tasks need the generated parser, except when the build excludes
# the backend (the same signal ext/prism/extconf.rb reads). compile:prism is
# hooked separately: the typecheck tasks invoke it directly, bypassing
# :compile. Prepended, not appended: prerequisites run in declaration order,
# and the extension's own chain runs extconf, which refuses to configure
# without the generated parser.
unless ENV["PRISM_PARSEY"] == "0"
  task compile: PARSEY_SOURCE if Rake::Task.task_defined?(:compile)
  if Rake::Task.task_defined?("compile:prism")
    Rake::Task["compile:prism"].prerequisites.unshift(PARSEY_SOURCE)
  end
end
