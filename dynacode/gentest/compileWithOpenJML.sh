#!/bin/bash

if [ -e "./openjml.jar" ] 
then
   if [ -e "./objenesis-2.2.jar" ]
   then
      java -jar ./openjml.jar -cp "../objenesis-2.2.jar" -rac *.java
   else
      echo "objenesis-2.2.jar not found!"
   fi
else
   echo "openjml.jar not found!"
   echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"
   echo "Copy openjml.jar into the directory with test files."
fi
