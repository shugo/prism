# frozen_string_literal: true

source "https://rubygems.org"

gemspec

gem "benchmark-ips"
gem "parser"
gem "rake"
gem "rake-compiler"
gem "rake-compiler-dock", "~> 1.12.0"
gem "ruby_parser"
gem "test-unit"

platforms :mri, :windows do
  gem "ffi"
  gem "irb"
  gem "ruby_memcheck"
  gem "rdoc"
end

gem "onigmo", platforms: :ruby

# The parse.y backend's parser generator, needed only to edit its grammar.
gem "lrama", "0.8.0"

# Until a nokogiri release includes sparklemotion/nokogiri#3530, aarch64-mingw-ucrt
# source-builds of libxml2 fail in libtool. Pin to main on that platform only.
if RUBY_PLATFORM =~ /aarch64.*mingw/
  gem "nokogiri", github: "sparklemotion/nokogiri", branch: "main"
end
