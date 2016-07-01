/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof;

import org.key_project.util.properties.Properties;


/**
 *
 * @author christoph
 */
public interface StrategyInfoUndoMethod {

    void undo(Properties strategyInfos);
}
