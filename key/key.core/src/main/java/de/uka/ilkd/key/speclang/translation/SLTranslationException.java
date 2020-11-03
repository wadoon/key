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

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.Locatable;

import java.net.MalformedURLException;

public class SLTranslationException extends ProofInputException implements Locatable {

    private static final long serialVersionUID = 1L;

    private final String fileName;
    private final Position pos;

   public SLTranslationException(String message, Throwable cause,
         String fileName, Position pos) {
      super(message, cause);
      assert fileName != null;
      assert pos != null;
      this.fileName = fileName;
      this.pos = pos;
   }

   public SLTranslationException(String message, String fileName, Position pos,
         Throwable cause) {
      this(message, cause, fileName, pos);
   }

   public SLTranslationException(String message, String fileName, Position pos) {
      this(message, null, fileName, pos);
   }

   public SLTranslationException(String message, String fileName, int line,
         int column) {
      this(message, null, fileName, new Position(line, column));
   }

   public SLTranslationException(String message) {
      this(message, null, "no file", Position.UNDEFINED);
   }

   public SLTranslationException(String message, Throwable cause) {
      this(message);
   }

   public String getFileName() {
      return fileName;
   }

   public Position getPosition() {
      return pos;
   }

   public int getLine() {
      return pos.getLine();
   }

   public int getColumn() {
      return pos.getColumn();
   }

   @Override
   public Location getLocation() throws MalformedURLException {
      return new Location(getFileName(), getLine(), getColumn());
   }
}