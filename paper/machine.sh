#!/usr/bin/env bash
# Records the processor, the memory and the software versions of the machine the computations ran on.
lscpu | grep -E '^(Model name|CPU\(s\)|Thread\(s\) per core|Core\(s\) per socket):'
free -g | awk '/^Mem:/ {print "Memory (GB):", $2}'
echo "PARI/GP: $(echo 'version()' | gp -q)"
echo "Sage: $(sage --version 2>/dev/null)"
echo "Lean toolchain: $(cat ../lean-toolchain)"
