/**
 * 
 */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.common.core.logic.Name;

/**
 *
 */
public final class MetaShiftRight extends MetaShift {

	/**
	 * @param leftShift
	 */
	public MetaShiftRight() {
		super(new Name("#ShiftRight"));
	}

	@Override
    protected BigInteger shiftOp(BigInteger left, BigInteger right) {
        return left.shiftRight(right.intValue());
    }

}
