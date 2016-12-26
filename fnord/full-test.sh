#!/bin/sh

## this is terrible ;)
## again d3-int pretends to be d0-int as we're too lazy and it's not the point and...
cat test1.cpr | ./cpr-to-d3.scm | guile d3-to-yarr.scm | guile yarr-to-d0.scm | guile d3-int.scm
cat test2.cpr | ./cpr-to-d3.scm | guile d3-to-yarr.scm | guile yarr-to-d0.scm | guile d3-int.scm
