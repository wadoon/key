package org.key_project.key.tptp;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

class TargetFile {
    static final String DEFAULT_SORT = "S";
    final Slot sorts = new Slot("\t", ";", "\n");
    final Slot functions = new Slot("\t", ";", "\n");
    final Slot predicates = new Slot("\t", ";", "\n");
    final Slot axioms = new Slot("\t", "", " & \n");
    final Slot prop = new Slot("\t", "", " & \n");

    public void writeTo(PrintWriter target) {
        target.format("""
                \\sorts {
                %s
                }
                                    
                \\predicates {
                %s
                }
                                    
                \\functions {
                %s                
                }
                                    
                \\problem { 
                %s 
                -> 
                %s
                }
                """, sorts, predicates, functions, axioms, prop
        );
    }

    static class Slot {
        private final List<String> strings = new ArrayList<>(64);
        private final String itemPrefix, itemPostfix, delimiter;

        Slot() {
            this("", "", ", ");
        }

        Slot(String itemPrefix, String itemPostfix, String delimiter) {
            this.itemPrefix = itemPrefix;
            this.itemPostfix = itemPostfix;
            this.delimiter = delimiter;
        }

        @Override
        public String toString() {
            return strings.stream()
                    .map(it -> itemPrefix + it + itemPostfix)
                    .collect(Collectors.joining(delimiter));
        }

        public boolean append(String s) {
            return strings.add(s);
        }

        public void ensure(String s) {
            if (!strings.contains(s)) {
                append(s);
            }
        }
    }
}
