Licensing
---------

RECODER is distributed under the GNU Library or Lesser General Public 
License (LGPL). Starting with RECODER 0.75, we redistribute some third 
party libraries (jar files). These libraries are: JUnit distributed 
under the Common Public License (CPL), BeanShell distributed under 
the GNU Library or Lesser General Public License (LGPL). The
ASM framework distributed under this license:
http://asm.objectweb.org/license.html
is in use as of Recoder 0.83.
These licenses can also be found in the subdirectory "licenses".

Installation Instructions
-------------------------

RECODER comes with two sets of build files: a GNU make based set of 
build files as well as an ANT build file.

To build RECODER using make, you need

- GNU make (some targets depend on Unix shell utilities)

- JDK 1.5 or later

Run "make" for a list of targets.
Run "make all" to compile everything, create the documentation and run
regressions tests, or "make buildall" to only compile everything.

To build RECODER using ANT, you need

- APACHE ANT

- JDK 1.5 or later

Please refer to the ANT users manual on how to use the provided build 
file.
