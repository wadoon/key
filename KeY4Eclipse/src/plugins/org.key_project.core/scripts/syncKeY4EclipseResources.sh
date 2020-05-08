#!/bin/sh

# copys rules, icons and other resources

cp -RT key/key.ui/build/resources/main KeY4Eclipse/src/plugins/org.key_project.ui/bin
cp -RT key/key.core/build/resources/main KeY4Eclipse/src/plugins/org.key_project.ui/bin

cp -RT key/key.ui/build/resources/main KeY4Eclipse/src/plugins/org.key_project.core/bin
cp -RT key/key.core/build/resources/main KeY4Eclipse/src/plugins/org.key_project.core/bin
