# frozen_string_literal: true

require_relative "test_helper"

module Prism
  # Parses every fixture with both the hand-written parser and the parse.y
  # backend and requires identical trees (compared through Node#inspect, which
  # covers node types, fields, flags, and byte locations) and, when both
  # backends parse without errors, identical warnings (type, location, level,
  # and message).
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
            parsey.value.inspect == hand.value.inspect &&
              warning_signature(parsey) == warning_signature(hand)
          end

        if excluded
          refute equivalent, "#{relative} passes now: remove it from test/prism/parsey/excludes.txt"
        elsif !equivalent
          flunk equivalence_failure_message(relative, hand, parsey)
        end
      end
    end

    private

    def warning_signature(result)
      result.warnings.map { |warning|
        [warning.location.start_offset, warning.location.end_offset, warning.level, warning.message]
      }.sort
    end

    def equivalence_failure_message(relative, hand, parsey)
      if parsey.errors.any? && hand.errors.none?
        "#{relative}: parse_y reports errors where the hand-written parser does not: " \
          "#{parsey.errors.map(&:message).uniq.join(", ")}"
      elsif parsey.errors.none? && hand.errors.any?
        "#{relative}: parse_y accepts source the hand-written parser rejects"
      elsif parsey.value.inspect != hand.value.inspect
        diff = parsey.value.inspect.lines.zip(hand.value.inspect.lines)
          .find { |(ours, theirs)| ours != theirs }
        "#{relative}: trees differ, first difference:\n  parse_y: #{diff[0]}  hand:    #{diff[1]}"
      else
        "#{relative}: warnings differ:\n" \
          "  parse_y: #{warning_signature(parsey)}\n  hand:    #{warning_signature(hand)}"
      end
    end
  end
end
