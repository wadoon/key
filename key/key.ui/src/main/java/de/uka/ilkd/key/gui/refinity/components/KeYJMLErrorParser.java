// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.refinity.components;

import java.util.Optional;

import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;

import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.relational.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;

/**
 * @author Dominic Steinhoefel
 */
public class KeYJMLErrorParser extends AbstractParser {
    private AEInstantiationModel instModel = null;
    private Optional<DefaultParserNotice> notice = null;

    public KeYJMLErrorParser(AEInstantiationModel instModel) {
        setModel(instModel);
    }

    public KeYJMLErrorParser(AERelationalModel relModel, boolean firstProgram) {
        setModel(relModel, firstProgram);
    }

    public void setModel(AEInstantiationModel instModel) {
        this.instModel = instModel;
    }

    public void setModel(AERelationalModel relModel, boolean firstProgram) {
        this.instModel = AEInstantiationModel.fromRelationalModel(relModel, firstProgram);
    }

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        final DefaultParseResult result = new DefaultParseResult(this);

        if (notice != null) {
            notice.ifPresent(result::addNotice);
            return result;
        }

        if (instModel == null) {
            return result;
        }

        KeyBridgeUtils.getFirstKeYJMLParserErrorMessage(instModel).ifPresent(t -> {
            notice = Optional.of(new DefaultParserNotice( //
                    this, t.first, t.second - 1, -1, 2));
        });

        if (notice == null) {
            notice = Optional.empty();
        }

        notice.ifPresent(result::addNotice);

        return result;
    }

}
