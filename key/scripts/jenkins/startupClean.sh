#!/bin/sh
export PATH=$PATH:/home/hudson/key/bin/
git clean -x -d -f -q

# clean the settings to start with a defined configuration
rm -rf /var/lib/jenkins/.key/ $HOME/.key


echo "=== CVC 4 ==="
cvc4 --version | head -n 3

echo "=== MATHSAT ==="
mathsat -version

echo "=== PRINCESS ==="
princess -logo +version

echo "=== VAMPIRE ==="
vampire --version

echo "=== YICES ==="
yices-smt2 --version

echo "=== z3 ==="
z3 -version
