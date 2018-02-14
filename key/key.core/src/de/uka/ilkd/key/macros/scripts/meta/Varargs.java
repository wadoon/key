package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface Varargs {
    Class as() default String.class;
    String prefix() default "";
}
