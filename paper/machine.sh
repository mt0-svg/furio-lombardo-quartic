#!/usr/bin/env bash
# Records the processor, the memory and the software versions of the machine the computations ran on.
# Memory: the installed size is the line "Installed memory"; the lines before it are what the system reads
# without root: the System RAM of the firmware memory map, the physical address range that lsmem counts
# (memory blocks of 2 GiB, the hole below 4 GiB included) and the total that the kernel can use (free).
lscpu | grep -E '^(Model name|CPU\(s\)|Thread\(s\) per core|Core\(s\) per socket):'
for d in /sys/firmware/memmap/*; do echo "$(cat "$d/type")|$(cat "$d/start")|$(cat "$d/end")"; done |
  awk -F'|' '$1 == "System RAM" { n += strtonum($3) - strtonum($2) + 1 } END { printf "Firmware memory map, System RAM (GiB): %.2f\n", n / 2^30 }'
lsmem --summary | awk -F': *' '/^Total online memory/ { print "lsmem, total online memory (address range): " $2 }'
free -b | awk '/^Mem:/ { printf "free, total usable by the kernel (GiB): %.1f\n", $2 / 2^30 }'
echo "Installed memory (the size of the installed modules, stated; the three lines above are what the system reads): 64 GB"
echo "PARI/GP: $(echo 'version()' | gp -q)"
echo "Sage: $(sage --version 2>/dev/null)"
echo "Lean toolchain: $(cat ../lean-toolchain)"
