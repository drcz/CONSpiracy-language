#!/bin/sh
# d3-int pretends to be d0 as d0 is a proper subset of d3 anyway...
cat d3-test1.d3 | guile d3-to-yarr.scm | guile yarr-to-d0.scm | guile d3-int.scm
cat d3-test2.d3 | guile d3-to-yarr.scm | guile yarr-to-d0.scm | guile d3-int.scm
## can't believe it actually works!

# however DERC will not be happy about it anyway as it does not know partially static datastructures...
# all this is getting way too weird, ad we didn't even apply CPS yet.
# perhaps we could use Y as a special form, but anyway that was not the point of the experiment.
# Yarr program is The Holy Name -- we can skip this point as well; though now it's time to learn a lot before we proceed.
