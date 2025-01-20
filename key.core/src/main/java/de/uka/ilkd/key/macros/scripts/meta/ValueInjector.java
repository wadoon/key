/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @author Alexander Weigl
 * @version 1 (29.03.17)
 */
public class ValueInjector {
    /**
     * A default instance
     *
     * @see #getInstance()
     */
    private static ValueInjector instance;

    /**
     * A mapping between desired types and suitable @{@link StringConverter}.
     * <p>
     * Should be
     *
     * <pre>
     * T --> StringConverter<T>
     * </pre>
     */
    private final Map<Class<?>, StringConverter<?>> converters = new HashMap<>();

    /**
     * Injects the given {@code arguments} in the {@code obj}. For more details see
     * {@link #inject(ProofScriptCommand, Object, Map)}
     *
     * @param command a proof script command
     * @param obj a parameter class with annotation
     * @param arguments a non-null map of string pairs
     * @param <T> an arbitrary type
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException an access on some reflection methods occurred
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException an converter could not translate the given value in arguments
     */
    public static <T> T injection(ProofScriptCommand<T> command, T obj,
            Map<String, Object> arguments) throws ArgumentRequiredException,
            InjectionReflectionException, NoSpecifiedConverterException, ConversionException {
        return getInstance().inject(command, obj, arguments);
    }

    /**
     * Returns the default instance of a {@link ValueInjector} Use with care. No multi-threading.
     *
     * @return a static reference to the default converter.
     * @see #createDefault()
     */
    public static ValueInjector getInstance() {
        if (instance == null) {
            instance = createDefault();
        }
        return instance;
    }

    /**
     * Returns a fresh instance of a {@link ValueInjector} with the support for basic primitive data
     * types.
     *
     * @return a fresh instance
     */
    public static ValueInjector createDefault() {
        return new ValueInjector();
    }

    /**
     * Injects the converted version of the given {@code arguments} in the given {@code obj}.
     *
     * @param command a proof script command
     * @param obj a non-null instance of a parameter class (with annotation)
     * @param arguments a non-null string map
     * @param <T> type safety
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException an access on some reflection methods occurred
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException an converter could not translate the given value in arguments
     * @see Option
     * @see Flag
     */
    public <T> T inject(ProofScriptCommand<T> command, T obj, Map<String, Object> arguments)
            throws InjectionReflectionException, NoSpecifiedConverterException, ArgumentRequiredException {
        List<ProofScriptArgument<T>> meta = ArgumentsLifter.inferScriptArguments(obj.getClass(), command);
        List<ProofScriptArgument<T>> varArgs = new ArrayList<>(meta.size());

        List<String> usedKeys = new ArrayList<>();

        for (ProofScriptArgument<T> arg : meta) {
            if (arg.hasVariableArguments()) {
                varArgs.add(arg);
            } else {
                injectIntoField(arg, arguments, obj);
                usedKeys.add(arg.getName());
            }
        }

        for (ProofScriptArgument<T> vararg : varArgs) {
            final Map<String, Object> map = getStringMap(obj, vararg);
            final int prefixLength = vararg.getName().length();
            for (Map.Entry<String, Object> e : arguments.entrySet()) {
                String k = e.getKey();
                Object v = e.getValue();
                if (!usedKeys.contains(k) && k.startsWith(vararg.getName())) {
                    map.put(k.substring(prefixLength), v);
                    usedKeys.add(k);
                }
            }
        }

        return obj;
    }

    @SuppressWarnings("unchecked")
    private Map<String, Object> getStringMap(Object obj, ProofScriptArgument<?> vararg)
            throws InjectionReflectionException {
        try {
            Map<String, Object> map = (Map<String, Object>) vararg.getField().get(obj);
            if (map == null) {
                map = new HashMap<>();
                vararg.getField().set(obj, map);
            }
            return map;
        } catch (IllegalAccessException e) {
            throw new InjectionReflectionException(
                "Error on using reflection on class " + obj.getClass(), e, vararg);
        }
    }

    private void injectIntoField(ProofScriptArgument<?> meta, Map<String, Object> args, Object obj)
            throws InjectionReflectionException, ArgumentRequiredException {
        final Object val = args.get(meta.getName());
        if (val == null) {
            if (meta.isRequired()) {
                throw new ArgumentRequiredException(String.format(
                    "Argument %s:%s is required, but %s was given. " + "For comamnd class: '%s'",
                    meta.getName(), meta.getField().getType(), null, meta.getCommand().getClass()),
                    meta);
            }
        } else {
            try {
                // FIXME: I had to add this, otherwise I would receive an illegal access exception.
                meta.getField().setAccessible(true);
                meta.getField().set(obj, val);
            } catch (IllegalAccessException e) {
                throw new InjectionReflectionException("Could not inject values via reflection", e,
                    meta);
            }
        }
    }
}
