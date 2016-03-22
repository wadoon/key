package de.uka.ilkd.key.nui;

import java.lang.annotation.Annotation;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * {@link Annotation} to easily add new menus to the main menu.
 * <p>
 * TODO explain how to add menus
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface KeYMenu {
    /**
     * Path to the FXML.
     */
    String path();

    /**
     * Menu in which this new menu should be added. Default is "" which adds the
     * menu as a new main menu.
     */
    String parentMenu() default "";
}