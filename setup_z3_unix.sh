#!/bin/bash
cd lib
wget http://research.microsoft.com/projects/z3/z3-4.0.tar.gz
tar xfz z3-4.0.tar.gz
rm z3-4.0.tar.gz
mv z3 z3-4.0
wget http://research.microsoft.com/projects/z3/z3-3.2.tar.gz
tar xfz z3-3.2.tar.gz
rm z3-3.2.tar.gz
