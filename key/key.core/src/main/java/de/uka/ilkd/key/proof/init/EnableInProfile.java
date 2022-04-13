package de.uka.ilkd.key.proof.init;

import java.lang.annotation.*;

/**
 * @author Alexander Weigl
 * @version 1 (21.03.22)
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
@Repeatable(value = EnableInProfiles.class)
public @interface EnableInProfile {
    Class<Profile> value();
}
