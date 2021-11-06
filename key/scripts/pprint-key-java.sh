#!/bin/sh

GRADLE="./gradlew"

if which gradle; then
  GRADLE="gradle"
fi

$GRADLE --parallel :key.ui:shadowJar

java -cp key.ui/build/libs/key-*exe.jar -jar de.uka.ilkd.key.java.helper.PPrint $*
