package de.uka.ilkd.key.nui;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface KeYMenu {
    String path();
    String[] windows() default "Main";
    String parentMenu() default "";
}
