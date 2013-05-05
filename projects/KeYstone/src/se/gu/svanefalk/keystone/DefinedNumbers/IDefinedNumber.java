package se.gu.svanefalk.keystone.DefinedNumbers;

/**
 * Represents a number which may or may not have been defined. One the number is
 * bound to a value, it is deemed defined for the remainder of its lifetime.
 * 
 * @author christopher
 * 
 */
public interface IDefinedNumber {

    boolean isDefined();
}
