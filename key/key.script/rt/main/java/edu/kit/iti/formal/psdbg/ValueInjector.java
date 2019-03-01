package edu.kit.iti.formal.psdbg;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.meta.*;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.interpreter.data.TermValue;
import lombok.RequiredArgsConstructor;
import lombok.Value;

import java.io.StringReader;
import java.lang.annotation.Retention;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
     * Should be <pre>T --> StringConverter<T></pre>
     */
    private List<ConverterWrapper> converters = new ArrayList<>();


    public static <T> T injection(ProofScriptCommand command, T obj, Map<String, Object> arguments)
            throws ArgumentRequiredException, InjectionReflectionException,
            NoSpecifiedConverterException, ConversionException {
        return getInstance().inject(command, obj, arguments);
    }

    /**
     * Returns the default instance of a {@link ValueInjector}
     * Use with care. No multi-threading.
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
     * Returns a fresh instance of a {@link ValueInjector} with the support
     * for basic primitive data types.
     *
     * @return a fresh instance
     */
    public static ValueInjector createDefault() {
        ValueInjector vi = new ValueInjector();
        vi.addConverter(Integer.class, Integer::parseInt);
        vi.addConverter(Long.class, Long::parseLong);
        vi.addConverter(Boolean.class, Boolean::parseBoolean);
        vi.addConverter(Double.class, Double::parseDouble);
        vi.addConverter(String.class, (String s) -> s);
        vi.addConverter(Boolean.TYPE, Boolean::parseBoolean);
        vi.addConverter(Byte.TYPE, Byte::parseByte);
        vi.addConverter(Character.TYPE, s -> s.charAt(0));
        vi.addConverter(Short.TYPE, Short::parseShort);
        vi.addConverter(Integer.TYPE, Integer::parseInt);
        vi.addConverter(Long.TYPE, Long::parseLong);
        vi.addConverter(Double.TYPE, Double::parseDouble);
        vi.addConverter(Float.TYPE, Float::parseFloat);
        vi.addConverter(BigInteger.class,Integer.class, (BigInteger b) -> b.intValue());
        vi.addConverter(BigInteger.class,Integer.TYPE, (BigInteger b) -> b.intValue());

        return vi;
    }

    public static ValueInjector createDefault(Node node) {
        ValueInjector valueInjector = createDefault();
        TermConverter termConverter = new TermConverter(node);
        valueInjector.addConverter(Sort.class, new SortConverter(node.proof()));
        valueInjector.addConverter(TermValue.class, Term.class, new TermValueConverter(node));
        valueInjector.addConverter(Term.class, termConverter);
        return valueInjector;
    }

    @Value
    public static class TermValueConverter implements Converter<TermValue, Term> {
        private Node node;

        @Override
        public Term convert(TermValue s) throws Exception {
            if (s.getTerm() != null) {
                return s.getTerm();
            } else {
                NamespaceSet nss = null;
                if(s.getNs() !=null) {
                    nss = s.getNs();

                }
                TermConverter converter = new TermConverter(node, nss);
                Term t = converter.convert(s.getTermRepr());
                s.setTerm(t);
                return t;
            }
        }
    }

    @RequiredArgsConstructor
    public static class TermConverter implements Converter<String, Term> {
        private final Node node;
        private final static DefaultTermParser PARSER = new DefaultTermParser();
        private NamespaceSet additionalNamespace;

        public TermConverter(Node node, NamespaceSet additionalNamespace) {
            this.node = node;
            this.additionalNamespace = additionalNamespace;
        }


        @Override
        public Term convert(String string) throws ParserException {
            StringReader reader = new StringReader(string);
            Services services = node.proof().getServices();

            //TODO check if local namespace is needed
            NamespaceSet ns;
            Goal g = node.proof().getGoal(node);
            if (g != null) {
                ns = g.getLocalNamespaces();
            } else {
                ns = node.proof().getNamespaces();
            }

            if(additionalNamespace!=null) {
                ns = ns.copy();
                ns.add(additionalNamespace);
            }

            Term formula = PARSER.parse(reader, null, services, ns, node.proof().abbreviations());

            return formula;
        }
    }

    @Value public static class SortConverter implements Converter<String, Sort>{
        private Proof proof;

        @Override
        public Sort convert(String sortName) {
            return proof.getServices().getNamespaces().sorts().lookup(sortName);
        }
    }


    /**
     * Injects the converted version of the given {@code arguments} in the given {@code obj}.
     *
     * @param command   a proof script command
     * @param obj       a non-null instance of a parameter class (with annotation)
     * @param arguments a non-null string map
     * @param <T>       type safety
     * @return the same object as {@code obj}
     * @throws ArgumentRequiredException     a required argument was not given in {@code arguments}
     * @throws InjectionReflectionException  an access on some reflection methods occured
     * @throws NoSpecifiedConverterException unknown type for the current converter map
     * @throws ConversionException           an converter could not translage the given value
     *                                       in {@arguments}
     * @see Option
     * @see Flag
     */
    public <T> T inject(ProofScriptCommand command, T obj, Map<String, Object> arguments)
            throws ConversionException, InjectionReflectionException, NoSpecifiedConverterException,
            ArgumentRequiredException {
        List<ProofScriptArgument> meta = ArgumentsLifter
                .inferScriptArguments(obj.getClass(), command);
        List<ProofScriptArgument> varArgs = new ArrayList<>(meta.size());

        List<String> usedKeys = new ArrayList<>();

        for (ProofScriptArgument arg : meta) {
            if (arg.hasVariableArguments()) {
                varArgs.add(arg);
            } else {
                injectIntoField(arg, arguments, obj);
                usedKeys.add(arg.getName());
            }
        }

        for (ProofScriptArgument vararg : varArgs) {
            final Map map = getStringMap(obj, vararg);
            final int prefixLength = vararg.getName().length();
            for (Map.Entry<String, Object> e : arguments.entrySet()) {
                String k = e.getKey();
                Object v = e.getValue();
                if (!usedKeys.contains(k) && k.startsWith(vararg.getName())) {
                    map.put(k.substring(prefixLength), convert(vararg, v));
                    usedKeys.add(k);
                }
            }
        }

        return obj;
    }

    private Map getStringMap(Object obj, ProofScriptArgument vararg)
            throws InjectionReflectionException {
        try {
            Map map = (Map) vararg.getField().get(obj);
            if (map == null) {
                map = new HashMap();
                vararg.getField().set(obj, map);
            }
            return map;
        } catch (IllegalAccessException e) {
            throw new InjectionReflectionException(
                    "Error on using reflection on class " + obj.getClass(), e, vararg);
        }
    }

    private void injectIntoField(ProofScriptArgument meta, Map<String, Object> args, Object obj)
            throws InjectionReflectionException, ArgumentRequiredException,
            ConversionException, NoSpecifiedConverterException {
        final Object val = args.get(meta.getName());
        if (val == null) {
            if (meta.isRequired()) {
                throw new ArgumentRequiredException(
                        String.format("Argument %s:%s is required, but %s was given. " +
                                        "For comamnd class: '%s'",
                                meta.getName(), meta.getField().getType(), val,
                                meta.getCommand().getClass()), meta);
            }
        } else {
            Object value = convert(meta, val);
            try {
                //if (meta.getType() != value.getClass())
                //    throw new ConversionException("The typed returned '" + val.getClass()
                //            + "' from the converter mismtached with the
                // type of the field " + meta.getType(), meta);
                meta.getField().set(obj, value);
            } catch (IllegalAccessException e) {
                throw new InjectionReflectionException("Could not inject values via reflection",
                        e, meta);
            }
        }
    }

    @SuppressWarnings("unchecked")
    private Object convert(ProofScriptArgument meta, Object val)
            throws NoSpecifiedConverterException, ConversionException {
        Converter converter = getConverter(val.getClass(), meta.getType());
        if (converter == null) {
            throw new NoSpecifiedConverterException("No converter registered for class: " +
                    meta.getField().getType(), meta);
        }
        try {
            return converter.convert(val);
        } catch (Exception e) {
            throw new ConversionException(
                    String.format("Could not convert value %s to type %s",
                            val, meta.getField().getType()), e, meta);
        }
    }

    /**
     * Registers the given converter for the specified class.
     *
     * @param conv  a converter for the given class
     * @param <T>   an arbitrary type
     */
    public <T,R> void addConverter(Class<T> from, Class<R> to, Converter<T,R> conv) {
        converters.add(new ConverterWrapper<T,R>(from, to, conv));
    }

    public <R> void addConverter(Class<R> to, Converter<String,R> conv) {
        addConverter(String.class, to, conv);
    }

    public <T,R> void addConverter(Converter<T,R> conv) {
        Method[] ms = conv.getClass().getMethods();
        for (Method m : ms) {
            if (m.getParameterCount() == 1) {
                Class<T> t = (Class<T>) m.getParameterTypes()[0];
                Class<R> c = (Class<R>) m.getReturnType();
                addConverter(t,c, conv);
            }
        }

    }

    /**
     * Finds a converter for the given class.
     * @return null or a suitable converter (registered) converter for the requested class.
     */
    @SuppressWarnings("unchecked")
    public <T,R> Converter<T,R> getConverter(Class<T> from, Class<R> to) {
        for (ConverterWrapper c: converters) {
                if(c.getFrom().equals(from) && c.getTo().equals(to))
                    return c.getConverter();
       }
        throw new RuntimeException("Could not find a suitable converter for types " + from + " to " + to);
    }


    @Value
    private static class ConverterWrapper<T,R> {
        Class<T> from;
        Class<R> to;
        Converter<T,R> converter;
    }

    interface  Converter<T, R> {
        R convert(T o) throws Exception;
    }
}
