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

package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * @since 1.7.2118
 * @author bruns
 *
 */
public class OrdLim extends Operator {

    private static final long serialVersionUID = 0;


    public OrdLim(Expression seq) {
        super(seq);
        makeParentRoleValid();
    }


    protected OrdLim(OrdLim proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override    
    public OrdLim deepClone() {
        return new OrdLim(this);
    }


    @Override    
    public int getArity() {
        return 1;
    }


    @Override    
    public int getPrecedence() {
        return 0;
    }


    @Override    
    public int getNotation() {
        return PREFIX;
    }


    @Override    
    public void accept(SourceVisitor v) {

    }
    
    public String toSource(){
        return "\\ord_lim("+children.get(0).toSource()+")";
    }

}