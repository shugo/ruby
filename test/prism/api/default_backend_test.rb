# frozen_string_literal: true

require_relative "../test_helper"

module Prism
  class DefaultBackendTest < TestCase
    # Wordings the two backends use to reject the probe snippet "a=>".
    PRISM_MESSAGE = "expected a pattern expression after `=>`"
    PARSE_Y_MESSAGE = "unexpected end-of-input"

    def test_pinned_by_test_helper
      assert_equal :prism, Prism.default_backend
      assert_equal PRISM_MESSAGE, probe_message
    end

    def test_invalid_backend
      assert_raise(ArgumentError) { Prism.default_backend = :handwritten }
    end

    def test_parse_y_requires_the_backend
      unless parsey_available?
        assert_raise(ArgumentError) { Prism.default_backend = :parse_y }
      end
    end

    def test_selects_backend
      return unless parsey_available?

      Prism.default_backend = :parse_y
      assert_equal :parse_y, Prism.default_backend
      assert_equal PARSE_Y_MESSAGE, probe_message

      Prism.default_backend = :prism
      assert_equal PRISM_MESSAGE, probe_message
    end

    def test_explicit_backend_option_wins
      return unless parsey_available?

      Prism.default_backend = :parse_y
      assert_equal PRISM_MESSAGE, probe_message(backend: :prism)
    end

    def test_wins_over_environment_variable
      return unless parsey_available?

      saved = ENV["PRISM_PARSER_BACKEND"]
      ENV["PRISM_PARSER_BACKEND"] = "parse_y"
      assert_equal PRISM_MESSAGE, probe_message

      ENV["PRISM_PARSER_BACKEND"] = "prism"
      Prism.default_backend = :parse_y
      assert_equal PARSE_Y_MESSAGE, probe_message
    ensure
      ENV["PRISM_PARSER_BACKEND"] = saved
    end

    def test_nil_restores_environment_default
      return unless parsey_available?

      saved = ENV["PRISM_PARSER_BACKEND"]
      ENV["PRISM_PARSER_BACKEND"] = "parse_y"
      Prism.default_backend = nil
      assert_equal PARSE_Y_MESSAGE, probe_message
    ensure
      ENV["PRISM_PARSER_BACKEND"] = saved
    end

    private

    def parsey_available?
      Prism.respond_to?(:backends) && Prism.backends.include?(:parse_y)
    end

    def probe_message(**options)
      Prism.parse("a=>", **options).errors.first.message
    end
  end
end
