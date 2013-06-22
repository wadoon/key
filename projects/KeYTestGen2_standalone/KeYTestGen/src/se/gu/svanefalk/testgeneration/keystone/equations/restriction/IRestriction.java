package se.gu.svanefalk.testgeneration.keystone.equations.restriction;

import org.apache.commons.math3.fraction.Fraction;

public interface IRestriction {

    Fraction makeConform(Fraction value);
}
