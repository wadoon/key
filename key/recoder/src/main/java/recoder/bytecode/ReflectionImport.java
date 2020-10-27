package recoder.bytecode;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

public class ReflectionImport {
    private static String getTypeName(Class c) {
        String n = c.getName();
        if (n.charAt(0) == '[')
            try {
                n = ByteCodeParser.decodeType(n);
            } catch (ByteCodeFormatException bcfe) {
                System.err.println("Internal error: " + bcfe);
            }
        return n;
    }

    private static String[] getTypeNames(Class[] classes) {
        String[] names = new String[classes.length];
        for (int i = 0; i < names.length; i++)
            names[i] = getTypeName(classes[i]);
        return names;
    }

    private static String getShortName(String name) {
        return name.substring(name.lastIndexOf('.') + 1);
    }

    public static ClassFile getClassFile(String classname) {
        classname = classname.replace('$', '.');
        Class<?> c = null;
        try {
            c = Class.forName(classname);
        } catch (ClassNotFoundException cnfe) {
            return null;
        }
        ClassFile cf = new ClassFile();
        String n = c.getName();
        cf.setPhysicalName(n);
        cf.setFullName(n);
        cf.setName(getShortName(n));
        Class<?> sup = c.getSuperclass();
        if (sup != null)
            cf.setSuperName(sup.getName());
        cf.setAccessFlags(c.getModifiers() | (c.isAnnotation() ? 8192 : 0) | (c.isEnum() ? 16384 : 0));
        cf.setInterfaceNames(getTypeNames(c.getInterfaces()));
        Field[] dfields = c.getDeclaredFields();
        List<FieldInfo> fields = new ArrayList<FieldInfo>(dfields.length);
        for (int i = 0; i < dfields.length; i++) {
            Field f = dfields[i];
            int mods = f.getModifiers();
            String cvalue = null;
            if (Modifier.isFinal(mods) && Modifier.isStatic(mods))
                try {
                    f.setAccessible(true);
                    cvalue = f.get(null).toString();
                } catch (IllegalAccessException iae) {
                    throw new RuntimeException("Encountered IllegalAccessException during reflection import! Cause: ", iae);
                }
            fields.add(new FieldInfo(f.getModifiers(), f.getName(), getTypeName(f.getType()), cf, cvalue, null));
        }
        cf.setFields(fields);
        Constructor[] dconstructors = c.getDeclaredConstructors();
        List<ConstructorInfo> constructors = new ArrayList<ConstructorInfo>(dconstructors.length);
        for (int j = 0; j < dconstructors.length; j++) {
            Constructor co = dconstructors[j];
            constructors.add(new ConstructorInfo(co.getModifiers(), getShortName(co.getName()), getTypeNames(co.getParameterTypes()), getTypeNames(co.getExceptionTypes()), cf));
        }
        cf.setConstructors(constructors);
        Method[] dmethods = c.getDeclaredMethods();
        List<MethodInfo> methods = new ArrayList<MethodInfo>(dmethods.length);
        for (int k = 0; k < dmethods.length; k++) {
            Method m = dmethods[k];
            if (c.isAnnotation()) {
                methods.add(new AnnotationPropertyInfo(m.getModifiers(), getTypeName(m.getReturnType()), m.getName(), cf, m.getDefaultValue()));
            } else {
                methods.add(new MethodInfo(m.getModifiers(), getTypeName(m.getReturnType()), m.getName(), getTypeNames(m.getParameterTypes()), getTypeNames(m.getExceptionTypes()), cf));
            }
        }
        cf.setMethods(methods);
        cf.setInnerClassNames(getTypeNames(c.getDeclaredClasses()));
        return cf;
    }
}
