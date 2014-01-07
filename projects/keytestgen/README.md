KeYTestGen is an automated test case generation system for the
JavaCard programming language, which almost (almost!) means
that it supports the nice and juicy bits of the core Java 1.5. 

KTG works by using the symbolic execution engine of the KeY
system (www.key-project.org) in order to understand what
paths may be taken through a programs execution tree at
runtime. Based on this information, it isolates a set of
leaves on the tree which are then used as the basis for
test case generation. The system deduces what conditions
must be binding on the pre-state of the program in order for
each leave to be reached, and generates a test case for 
each one of them, satisfying this constraint.

KTG is meant to be flexible and support a wide array of 
target frameworks for test case generation. Currently, basic
support for JUnit4 is is the main concern, but this will
grow over time.

You can see a Prezi which provides an overview here:
http://prezi.com/byvnxmmikjyj/keytestgen2/


Help!!
======
I have very little spare time to develop KTG in, but I would
very much love to see this project grow to its full potential.
If you are willing to join in, I would be more than happy to
hear from you!
