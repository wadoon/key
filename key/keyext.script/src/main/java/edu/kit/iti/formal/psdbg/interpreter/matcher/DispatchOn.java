package edu.kit.iti.formal.psdbg.interpreter.matcher;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
public @interface DispatchOn {
    Class<?> value();
}
