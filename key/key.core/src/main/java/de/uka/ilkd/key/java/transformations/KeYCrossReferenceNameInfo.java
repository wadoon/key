// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.util.Debug;
import recoder.ServiceConfiguration;
import recoder.abstraction.ReferenceType;
import recoder.abstraction.Type;
import recoder.java.declaration.TypeDeclaration;
import recoder.kit.UnitKit;
import recoder.service.DefaultNameInfo;

import java.util.HashMap;
import java.util.LinkedHashMap;


/**
 * This is a specialisation of the NameInfo interface which allows KeY to detect
 * multiple declaration of types. It stores all defined type (w/o possible some
 * array types which do not matter) in a hash table to look up.
 * <p>
 * If it records an attempt to register a declaration type twice, a verbose
 * conversion exception is thrown.
 * <p>
 * It also reports a missing "java.lang.Object" definition in a
 * {@link ConvertException}. Recoder itself usually fails at a random point
 * with a {@link NullPointerException}.
 * <p>
 * An instance of this class is created in
 * {@link KeYTransformationPipelineServices}.
 *
 * @author MU
 */
public class KeYCrossReferenceNameInfo extends DefaultNameInfo {

    // this somewhat doubles name2type in DefaultNameInfo to which we have no access
    private final HashMap<String, ReferenceType> ReferenceTypes = new LinkedHashMap<String, ReferenceType>();

    public KeYCrossReferenceNameInfo(ServiceConfiguration config) {
        super(config);
    }

    /**
     * register a class type.
     *
     * @param ct class type to register
     * @throws ConvertException if there was already a different type registered for the
     *                          same name
     */
    @Override
    public void register(ReferenceType ct) {

        String name = ct.getFullName();
        ReferenceType old = ReferenceTypes.get(name);
        if (old != null && ct != old) {
            String d1, d2;
            if (ct instanceof TypeDeclaration) {
                d1 = UnitKit.getCompilationUnit((TypeDeclaration) ct).getOriginalDataLocation().toString();
            } else {
                d1 = ct.toString();
            }
            if (old instanceof TypeDeclaration) {
                d2 = UnitKit.getCompilationUnit((TypeDeclaration) old).getOriginalDataLocation().toString();
            } else {
                d2 = old.toString();
            }
            Debug.log4jWarn("Datatype " + name + " declared twice: Once in " + d1 + " and once in " + d2 + ", Keeping one from " + d2,
                    KeYCrossReferenceNameInfo.class.getName());
            return;
        }

        super.register(ct);

        ReferenceTypes.put(name, ct);
    }

    /**
     * unregister a class type. This happens for instance when removing an
     * EnumDeclaration and inserting an EnumTypeDeclaration<?> instead
     *
     * @param fullname name of the type to be unregistered
     */
    @Override
    public void unregisterReferenceType(String fullname) {
        super.unregisterReferenceType(fullname);
        ReferenceTypes.remove(fullname);
    }

    /*
     * just to make sure that ReferenceTypes captures all non-array types.
     */
    @Override
    public Type getType(String name) {
        Type t = super.getType(name);
        if (t instanceof ReferenceType)
            ReferenceTypes.put(name, (ReferenceType) t);
        return t;
    }

    /**
     * {@inheritDoc}
     * <p>
     * This implementation checks whether an implementation is available and
     * fails if not.
     *
     * @throws ConvertException if no implementation of java.lang.Object is available
     *                          presently.
     */
    @Override
    public ReferenceType getJavaLangObject() throws ConvertException {
        ReferenceType result = super.getJavaLangObject();
        if (result == null)
            throw new ConvertException("Class type 'java.lang.Object' cannot be found");
        return result;
    }
}