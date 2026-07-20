# frozen_string_literal: true

require_relative "test_helper"

# The whole file verifies the parse.y backend against the hand-written
# parser, so a build without it has nothing to test.
return unless Prism.respond_to?(:backends) && Prism.backends.include?(:parse_y)

module Prism
  # Token lengths that fall on the lexer's token buffer boundaries. The buffer
  # starts at 60 bytes and doubles, and the backend copies a whole identifier
  # run into it at once, so a token can land exactly on the end of the buffer.
  # Overrunning it by the terminator alone corrupts the heap silently; these
  # parses are what the sanitizer builds have to walk over.
  class ParseyLexerTest < TestCase
    LENGTHS = [59, 60, 61, 119, 120, 121, 239, 240, 241, 480, 960].freeze

    LENGTHS.each do |length|
      define_method(:"test_identifier_of_#{length}_bytes") do
        assert_backends_agree("#{"a" * length} = 1")
      end

      define_method(:"test_constant_of_#{length}_bytes") do
        assert_backends_agree("#{"A" * length} = 1")
      end

      define_method(:"test_symbol_of_#{length}_bytes") do
        assert_backends_agree(":#{"a" * length}")
      end

      define_method(:"test_method_name_of_#{length}_bytes") do
        assert_backends_agree("def #{"a" * length}; end")
      end
    end

    private

    def assert_backends_agree(source)
      hand = Prism.parse(source, backend: :prism)
      parsey = Prism.parse(source, backend: :parse_y)

      assert_empty parsey.errors.map(&:message)
      assert_equal hand.value.inspect, parsey.value.inspect
    end
  end
end
