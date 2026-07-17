# frozen_string_literal: true

source "https://rubygems.org"

gemspec

gem "benchmark-ips"
gem "parser"
gem "rake"
gem "rake-compiler"
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
