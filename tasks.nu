def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  build    compile the Lean library"
    print "  cache    fetch prebuilt mathlib artifacts"
    print "  check    evaluate the flake and run its checks"
    print "  fmt      rewrite the tree with the flake's formatters"
}

# Compile the Lean library
def "main build" [] {
    lake build
}

# Fetch prebuilt mathlib artifacts (run after changing lean-toolchain or the mathlib rev)
def "main cache" [] {
    lake exe cache get
}

# Evaluate the flake and run its checks
def "main check" [] {
    nix flake check
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}
