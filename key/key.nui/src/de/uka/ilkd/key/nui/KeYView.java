package de.uka.ilkd.key.nui;

import java.lang.annotation.Annotation;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * {@link Annotation} to easily create main menu entries and set some general
 * settings for a {@link ViewController}.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface KeYView {
    /**
     * Text of the menu entry.
     */
    String title();

    /**
     * Path (as String) to the FXML file of the view.
     */
    String path();

    /**
     * Position in which the view is displayed as default. {@link ViewPosition}
     */
    ViewPosition preferredPosition() default ViewPosition.CENTER;

    /**
     * Shortcut KeyCombination (as String) default "" will be ignored.
     */
    String accelerator() default "";

    /**
     * Indicates, if a menu entry should be added for this view.
     */
    boolean hasMenuItem() default true;

    /**
     * Indicates, if the view is active with default settings.
     */
    boolean defaultActive() default true;
    
    boolean isDebugView() default false;
}
