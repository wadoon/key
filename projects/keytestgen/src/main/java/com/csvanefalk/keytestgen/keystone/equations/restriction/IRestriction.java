package com.csvanefalk.keytestgen.keystone.equations.restriction;

import org.apache.commons.math3.fraction.Fraction;

public interface IRestriction {

    Fraction makeConform(Fraction value);
}
