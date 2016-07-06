// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.theories;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.services.BCTermServices;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.theories.CCIntegerTheory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class IntegerTheory extends CCIntegerTheory<Term> {

    private final Function sharp;
    private final Function numberSymbol[] = new Function[10];
    private final Function neglit;
    private final Function numbers;

    /**
     * TODO: Document.
     *
     * @param services
     */
    protected IntegerTheory(BCTermServices services) {
        super(services);
        
        // initialize caches for function symbols from integerHeader.key
        sharp = addFunction(services, "#");
        for (int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(services, "" + i);
        }
        neglit = addFunction(services, NEGATIVE_LITERAL_STRING);
        numbers = addFunction(services, NUMBERS_NAME.toString());
        assert sharp.sort() == numbers.argSort(0);
    }

    public Term toZTerm(String intStr, BCTermServices services) {
        int length = 0;
        boolean minusFlag = false;

        char[] int_ch = null;
        assert sharp != null;
        Term result = services.getTermBuilder().func(sharp);

        Function identifier = numbers;

        if (intStr.charAt(0) == '-') {
            minusFlag = true;
            intStr =
                    intStr.substring(1);
        }
        // We have to deal with literals coming both from programs and
        // the logic. The former can have prefixes ("0" for octal,
        // "0x" for hex) and suffixes ("L" for long literal). The latter
        // do not have any of these but can have arbitrary length.

        int_ch = intStr.toCharArray();
        length = int_ch.length;

        for (int i = 0; i < length; i++) {
            result =
                    services.getTermBuilder().func(
                            numberSymbol[int_ch[i] - '0'], result);
        }
        if (minusFlag) {
            result = services.getTermBuilder().func(neglit, result);
        }

        return services.getTermBuilder().func(identifier, result);
    }

}
