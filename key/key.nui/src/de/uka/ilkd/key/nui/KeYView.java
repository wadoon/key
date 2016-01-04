package de.uka.ilkd.key.nui;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface KeYView {
    /**
     * Text of the menu entry
     */
    String title();
    
    /**
     * Url to the fxml file of the view
     */
    String path();
    
// not used yet
//    String windows() default "Main";
    
    /**
     * Positon in which the view is displayed as default
     */
    ViewPosition preferredPosition() default ViewPosition.CENTER;
    
    /**
     * Shortcut KeyCombination (as String)
     * default "" will be ignored
     */
    String accelerator() default ""; 
    
    boolean hasMenuItem() default true;
}
