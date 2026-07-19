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
      sh "ruby #{id2token} #{grammar} | #{lrama} -o#{File.basename(PARSEY_SOURCE)} -H#{File.basename(PARSEY_HEADER)} - #{grammar}"
    end
  end
end

file PARSEY_SOURCE => [PARSEY_GRAMMAR, PARSEY_IDDEF, PARSEY_ID2TOKEN] do
  Rake::Task["parsey:generate"].invoke
end

file PARSEY_HEADER => PARSEY_SOURCE

# The compile task needs the generated parser, except when the build excludes
# the backend (the same signal ext/prism/extconf.rb reads).
unless ENV["PRISM_PARSEY"] == "0"
  task compile: PARSEY_SOURCE if Rake::Task.task_defined?(:compile)
end
