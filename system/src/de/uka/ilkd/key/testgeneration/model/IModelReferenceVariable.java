package de.uka.ilkd.key.testgeneration.model;

import java.util.List;

/**
 * Represents a reference type variable, which has a package declaration and set
 * of fields in addition to the attributes defined by {@link IModelVariable}
 * 
 * @author christopher
 */
interface IModelReferenceVariable
        extends IModelVariable {

    String getPackage();

    List<IModelVariable> getFields();
}
