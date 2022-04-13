package de.uka.ilkd.key.proof.init;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * @author Alexander Weigl
 * @version 1 (21.03.22)
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface EnableInProfiles {
    Class<? extends Profile>[] value();
}