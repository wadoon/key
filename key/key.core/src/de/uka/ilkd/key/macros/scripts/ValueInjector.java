package de.uka.ilkd.key.macros.scripts;

import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (29.03.17)
 */
public class ValueInjector {
    private Map<Class, Converter> converters = new HashMap<>();
    private static ValueInjector INSTANCE;

    public <T> T inject(T obj, Map<String, String> arguments) throws Exception {
        for (java.lang.reflect.Field field : obj.getClass().getFields()) {
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                injectIntoField(arguments.get(option.value()), obj, field);
            }

            Flag flag = field.getDeclaredAnnotation(Flag.class);
            if(flag!=null){
                //TODO handle flag
            }
        }
        return obj;
    }

    private <T> void injectIntoField(String s, T obj, Field field)
            throws Exception {
        Converter converter = getConverter(s.getClass());
        if (converter == null)
            throw new ScriptException(
                    "No converter registered for class: " + s.getClass());

        Object value = converter.convert(s);
        field.set(obj, value);
    }

    public static <T> T injection(T obj, Map<String, String> arguments)
            throws Exception {
        return getInstance().inject(obj, arguments);
    }

    public static ValueInjector getInstance() {
        if (INSTANCE == null)
            INSTANCE = createDefault();
        return INSTANCE;
    }

    public static ValueInjector createDefault() {
        ValueInjector vi = new ValueInjector();
        vi.addConverter(Integer.class, Integer::parseInt);
        vi.addConverter(Long.class, Long::parseLong);
        vi.addConverter(Boolean.class, Boolean::parseBoolean);
        vi.addConverter(Double.class, Double::parseDouble);
        vi.addConverter(String.class, (String s) -> s);
        return vi;
    }

    public <T> void addConverter(Class<T> clazz, Converter<T> conv) {
        converters.put(clazz, conv);
    }

    @SuppressWarnings("unchecked") public <T> Converter<T> getConverter(
            Class<T> clazz) {
        return (Converter<T>) converters.get(clazz);
    }

    /**
     * @param <T>
     */
    public static interface Converter<T> {
        T convert(String s) throws Exception;
    }

    /**
     *
     */
    public @interface Option {
        String value();
    }

    public @interface Flag {
        String arg();
        String value();
    }
}
