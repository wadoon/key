#!/bin/sh
export PATH=$PATH:/home/hudson/key/bin/
git clean -x -d -f -q

# clean the settings to start with a defined configuration
rm -rf /var/lib/jenkins/.key/ $HOME/.key


cvc4 --version
mathsat -version
princess --version
vampire --version
yices-smt2 --version
z3 -version
