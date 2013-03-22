package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.speclang.SpecificationElement;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 15:59
 * To change this template use File | Settings | File Templates.
 */
public interface InterfaceInvariant extends SpecificationElement {

    Term getInvariant(SchemaVariable historySV, IServices services);

    Term getOriginalInvariant();

}
