# frozen_string_literal: true

return if RUBY_VERSION < "3.3.0"

require_relative "test_helper"

# The whole file verifies the parse.y backend against the hand-written
# parser, so a build without it has nothing to test.
# Prism.backends might also be absent entirely: the gem install test runs
# this suite against whatever prism gem is installed, including older ones.
return unless Prism.respond_to?(:backends) && Prism.backends.include?(:parse_y)

# These files verify the repository's own build of the backend against the
# hand-written parser. When the suite runs against an installed gem (the gem
# packaging tests), that is not what is being tested; skip.
if defined?(Gem) && (spec = Gem.loaded_specs["prism"])
  repository = File.expand_path("../..", __dir__)
  return unless File.identical?(spec.full_gem_path, repository)
end

module Prism
  # Compares errors between the hand-written parser and the parse.y backend
  # over the error corpus (test/prism/errors), at each fixture's newest
  # applicable syntax version.
  #
  # Two ratchets:
  # - Both backends must agree that every fixture is invalid, except the
  #   fixtures in VALIDITY_EXCLUDES (version-gated checks of older syntax
  #   versions that the fork does not implement).
  # - Fixtures listed in parsey/error_matches.txt must produce byte-identical
  #   errors_format (same messages, locations, and order); the list grows as
  #   message parity improves.
  class ParseyErrorsTest < TestCase
    base = File.expand_path("errors", __dir__)

    # Version-gated checks of older syntax versions are ported; nothing is
    # currently excluded.
    VALIDITY_EXCLUDES = [].freeze

    matches = File.readlines(File.join(__dir__, "parsey", "error_matches.txt"), chomp: true)
      .reject { |line| line.empty? || line.start_with?("#") }

    Dir[File.join(base, "**", "*.txt")].sort.each do |path|
      relative = path.delete_prefix("#{base}/")

      define_method(:"test_#{relative}") do
        raw = File.read(path, binmode: true, external_encoding: Encoding::UTF_8)
        source = raw.lines.grep_v(/^\s*\^/).join.gsub(/\n*\z/, "")
        version = TestCase.ruby_versions_for(relative).last

        hand = Prism.parse(source, version: version, backend: :prism)
        parsey = Prism.parse(source, version: version, backend: :parse_y)

        if VALIDITY_EXCLUDES.include?(relative)
          refute_equal hand.errors.any?, parsey.errors.any?,
            "#{relative} agrees on validity now: remove it from VALIDITY_EXCLUDES"
          return
        end

        assert_equal hand.errors.any?, parsey.errors.any?,
          "expected both backends to agree that the source is invalid"

        if matches.include?(relative)
          assert_equal hand.errors_format, parsey.errors_format,
            "#{relative} no longer matches: fix the regression or remove it from test/prism/parsey/error_matches.txt"
        end
      end
    end
  end
end
