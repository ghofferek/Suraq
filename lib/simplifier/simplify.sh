#!/bin/bash
./lib/simplifier/aigtoaig $1 ./binary_aiger.aig
./lib/simplifier/abc -c "read_aiger ./binary_aiger.aig; strash; refactor; rewrite; dfraig; rewrite; dfraig; write_aiger -s simplified_binary_aiger.aig"
./lib/simplifier/aigtoaig -s simplified_binary_aiger.aig  $2

