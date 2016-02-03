package de.uka.ilkd.key.nui.viewmediation;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Provides save access to methods/functions of other views
 * @author Benedikt Gross
 *
 */
public class ViewDereferer {

    static List<DereferedViewProxy> actionObjects  = new LinkedList<>();

    public static <T extends DereferedViewProxy> void ExecuteMethodOnView(Class<T> type,
            Consumer<T> consumer) {
        ExecuteFunctionOnView(type, x -> {
            consumer.accept(x);
            return null;
        });
    }

    /**
     * 
     * @param type Make sure that this is the same type as "T"
     * @param func
     * @return
     */
    @SuppressWarnings("unchecked")
    public static <T extends DereferedViewProxy, R> R ExecuteFunctionOnView(Class<T> type,
            Function<T, R> func) {
        T aquieredProxy = null;
        for (DereferedViewProxy proxy : actionObjects) {
            if (proxy.getClass() == type) {
                aquieredProxy = (T) proxy;
                break;
            }
        }
        
        if (aquieredProxy == null)
            return null;

        return func.apply(aquieredProxy);
    }

    public static void attachActionObject(DereferedViewProxy proxy) {
        actionObjects.add(proxy);
    }

    public static void detachActionObject(DereferedViewProxy proxy) {
        actionObjects.remove(proxy);
    }
}
