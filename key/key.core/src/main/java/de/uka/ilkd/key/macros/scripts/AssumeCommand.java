package de.uka.ilkd.key.macros.scripts;

/**
 * The assume command takes one argument: a formula to which the command is
 * applied.
 * 
 * @see AxiomCommand The axiom command is a synonym for the assumes command.
 */
public class AssumeCommand extends AxiomCommand {
    @Override
    public String getName() {
        return "assume";
    }
}
