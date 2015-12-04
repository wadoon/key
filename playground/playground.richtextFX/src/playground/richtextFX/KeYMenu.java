package playground.richtextFX;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface KeYMenu {
    /**
     * Path to the fxml
     */
    String path();
    
  //  String[] windows() default "Main";
    
    /**
     * Menu in which this new menu should be added.
     * Default is "" which adds the menu as a new main menu
     */
    String parentMenu() default "";
}
