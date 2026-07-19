# Error-tolerance benchmark for the parse.y backend: mutates passing
# fixtures and compares recovery quality against the hand-written parser.
# Not part of the test suite; run manually:
#
#   ruby -Ilib test/prism/parsey/tolerance_bench.rb
#
require "prism"

def count_nodes(node)
  n = 1
  node.child_nodes.compact.each { |c| n += count_nodes(c) }
  n
end

base = File.expand_path("../fixtures", __dir__) + "/"
excludes = File.readlines(base + "../parsey/excludes.txt", chomp: true).reject { |l| l.empty? || l.start_with?("#") }
fixtures = Dir.glob(base + "**/*.txt").sort.map { |p| p.sub(base, "") } - excludes
srand(42)
sample = fixtures.sample(120)

mutations = {
  truncate:    ->(src) { src[0, (src.size * 0.6).to_i] },
  drop_end:    ->(src) { i = src.rindex(/^\s*end\b/); i ? src[0...i] + src[i..].sub(/end/, "") : nil },
  garbage:     ->(src) { lines = src.lines; return nil if lines.size < 2; lines.insert(lines.size / 2, "@@@ !!\n").join },
  drop_line:   ->(src) { lines = src.lines; return nil if lines.size < 3; lines.delete_at(lines.size / 2); lines.join },
  unbalanced:  ->(src) { i = src.index("("); i ? src[0...i] + src[i+1..] : nil },
}

stats = Hash.new { |h, k| h[k] = Hash.new(0) }
ratio_sum = Hash.new(0.0)
ratio_n = Hash.new(0)

sample.each do |rel|
  src = File.read(base + rel)
  mutations.each do |name, fn|
    broken = fn.call(src) rescue nil
    next unless broken && broken != src
    h = Prism.parse(broken) rescue next
    next if h.errors.empty?   # mutation still valid: skip
    st = stats[name]
    st[:cases] += 1

    y = nil
    pid = fork { Prism.parse(broken, backend: :parse_y); exit! 0 }
    _, status = Process.waitpid2(pid)
    if !status.success?
      st[:crash] += 1
      next
    end
    y = Prism.parse(broken, backend: :parse_y)

    st[:error_reported] += 1 if y.errors.any?
    hn = count_nodes(h.value)
    yn = count_nodes(y.value)
    st[:nonempty] += 1 if yn > 2 || hn <= 2
    r = hn > 0 ? [yn.to_f / hn, 1.0].min : 1.0
    ratio_sum[name] += r
    ratio_n[name] += 1
  end
end

puts "%-12s %6s %6s %9s %9s %10s" % %w[mutation cases crash err-rep nonempty node-ratio]
stats.each do |name, st|
  n = ratio_n[name]
  puts "%-12s %6d %6d %9d %9d %9.1f%%" % [name, st[:cases], st[:crash], st[:error_reported], st[:nonempty], n > 0 ? 100.0 * ratio_sum[name] / n : 0]
end
