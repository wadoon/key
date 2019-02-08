#!/bin/bash
if [ -e "./jmlruntime.jar" ]
then  if [ -e "./jmlspecs.jar" ]
  then
     if [ -e "./objenesis-2.2.jar" ]
     then
        if [ "$1" = "" ] ; then
           echo "Provide the test driver as an argument (without .java postfix). For example:"
           echo "  executeWithOpenJML.sh TestGeneric0 "
           echo "Make sure that jmlruntime.jar and jmlspecs.jar are in the"
           echo "current directory."
           quit
        else
           java -cp ./objenesis-2.2.jar:./jmlruntime.jar:./jmlspecs.jar:. $1
        fi
      else
         echo "objenesis-2.2.jar not found!"
      fi
else
  echo "jmlspecs.jar not found!"
  echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"
  echo "Copy jmlspecs.jar into the directory with test files."
  quit
fi
else
   echo "jmlruntime.jar not found!"
   echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"
   echo "Copy jmlruntime.jar into the directory with test files."
   quit
fi
