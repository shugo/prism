# frozen_string_literal: true

require_relative "test_helper"

module Prism
  # Parses every fixture with both the hand-written parser and the parse.y
  # backend and requires identical trees (compared through Node#inspect, which
  # covers node types, fields, flags, and byte locations).
  #
  # Fixtures listed in parsey/excludes.txt are known gaps: they are expected to
  # fail, and this test fails when one of them unexpectedly passes, so the list
  # only ever shrinks (a ratchet). Remove fixtures from the list as the backend
  # learns to handle them.
  class ParseyEquivalenceTest < TestCase
    base = File.join(__dir__, "fixtures")
    excludes = File.readlines(File.join(__dir__, "parsey", "excludes.txt"), chomp: true)
      .reject { |line| line.empty? || line.start_with?("#") }

    Dir[File.join(base, "**", "*.txt")].sort.each do |path|
      relative = path.delete_prefix("#{base}/")
      excluded = excludes.include?(relative)

      define_method(:"test_#{relative}") do
        source = File.read(path)

        hand = Prism.parse(source)
        parsey = Prism.parse(source, backend: :parse_y)

        equivalent =
          if parsey.errors.any? || hand.errors.any?
            # Error message and location parity is a later milestone; for now
            # both backends must simply agree that the source is invalid.
            parsey.errors.any? && hand.errors.any?
          else
            parsey.value.inspect == hand.value.inspect
          end

        if excluded
          refute equivalent, "#{relative} passes now: remove it from test/prism/parsey/excludes.txt"
        elsif !equivalent
          flunk equivalence_failure_message(relative, hand, parsey)
        end
      end
    end

    private

    def equivalence_failure_message(relative, hand, parsey)
      if parsey.errors.any? && hand.errors.none?
        "#{relative}: parse_y reports errors where the hand-written parser does not: " \
          "#{parsey.errors.map(&:message).uniq.join(", ")}"
      elsif parsey.errors.none? && hand.errors.any?
        "#{relative}: parse_y accepts source the hand-written parser rejects"
      else
        diff = parsey.value.inspect.lines.zip(hand.value.inspect.lines)
          .find { |(ours, theirs)| ours != theirs }
        "#{relative}: trees differ, first difference:\n  parse_y: #{diff[0]}  hand:    #{diff[1]}"
      end
    end
  end
end
