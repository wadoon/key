package de.uka.ilkd.key.nui.viewmediation;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

import de.uka.ilkd.key.nui.ViewController;

/**
 * Provides save access to methods/functions of other views <b>without</b> a proxy/wrapper
 * @author Benedikt Gross
 *
 */
public class ViewDerefererSlim {
    static List<ViewController> actionObjects  = new LinkedList<>();
    
    public static <T extends ViewController> void ExecuteMethodOnView(Class<T> type,
            Consumer<T> consumer) {
        ExecuteFunctionOnView(type, x -> {
            consumer.accept(x);
            return null;
        });
    }
    
    public static <T extends ViewController, R> R ExecuteFunctionOnView(Class<T> type,
            Function<T, R> func) {
        T aquieredObject = null;
        for (ViewController actionObject : actionObjects) {
            if (actionObject.getClass() == type) {
                aquieredObject = (T) actionObject;
                break;
            }
        }
        
        if (aquieredObject == null)
            return null;

        return func.apply(aquieredObject);
    }
    
    /**
     * Should not be called. This is used by the ViewInformation object to register for call receiving
     * @param actionObject
     */
    public static void attachActionObject(ViewController actionObject) {
        actionObjects.add(actionObject);
    }

    /**
     * Should not be called. This is used by the ViewInformation object to register for call receiving
     * @param actionObject
     */
    public static void detachActionObject(ViewController actionObject) {
        actionObjects.remove(actionObject);
    }
}
