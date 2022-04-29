package org.key_project.slicing;

import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.event.MouseWheelEvent;
import java.awt.event.MouseWheelListener;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;

public class PreviewDialog extends JDialog {
    public PreviewDialog(Window window, String dot) {
        super(window, "Preview");
        setLayout(new BorderLayout());
        var label = new JLabel("Running dot...");
        label.setBorder(new EmptyBorder(10,10,10,10));
        getContentPane().add(label);

        new DotExecutor(dot, window, this).execute();

        pack();
        setLocationRelativeTo(window);
        setVisible(true);
    }

    private static class DotExecutor extends SwingWorker<Void, Void> {
        private String error;
        private BufferedImage img;
        private String dot;
        private PreviewDialog dialog;
        private Window window;

        public DotExecutor(String dot, Window window, PreviewDialog dialog) {
            this.dot = dot;
            this.window = window;
            this.dialog = dialog;
        }

        @Override
        protected Void doInBackground() throws Exception {
            try {
                var process = new ProcessBuilder("dot", "-Tpng").start();
                var stdin = process.getOutputStream();
                stdin.write(dot.getBytes(StandardCharsets.UTF_8));
                stdin.close();
                byte[] output = process.getInputStream().readAllBytes();
                img = ImageIO.read(new ByteArrayInputStream(output));
                ImageIO.write(img, "PNG", new File("/tmp/x2.png"));
            } catch (IOException e) {
                error = e.getMessage();
            }
            return null;
        }

        @Override
        protected void done() {
            super.done();
            if (img != null) {
                dialog.getContentPane().removeAll();
                var pziv = new PanZoomImageView(img, 800, 600);
                pziv.setPreferredSize(new Dimension(800, 600));
                dialog.getContentPane().add(pziv, BorderLayout.CENTER);
                pziv.addMouseListener(pziv);
                pziv.addMouseMotionListener(pziv);
                pziv.addMouseWheelListener(pziv);
                dialog.pack();
                dialog.setLocationRelativeTo(window);
            } else {
                var label = new JLabel("Error: " + error);
                label.setBorder(new EmptyBorder(10,10,10,10));
                dialog.getContentPane().add(label);
            }
        }
    }

    private static class PanZoomImageView extends JComponent implements MouseListener, MouseMotionListener, MouseWheelListener {
        private final BufferedImage image;
        private final AffineTransform at;

        public PanZoomImageView(BufferedImage img, int width, int height) {
            this.image = img;

            int imageWidth = image.getWidth();
            int imageHeight = image.getHeight();
            double scale = 1.0;
            float scaleX = (float) width / imageWidth;
            float scaleY = (float) height / imageHeight;
            if (scaleX < 1.0 || scaleY < 1.0) {
                scale = Math.min(scaleX, scaleY);
            }
            var x = (width - scale * imageWidth) / 2;
            var y = (height - scale * imageHeight) / 2;
            at = AffineTransform.getScaleInstance(scale, scale);
            at.translate(x, y);
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);

            System.out.println("repaint " + System.currentTimeMillis());

            Graphics2D g2 = (Graphics2D) g;
            g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_BICUBIC);
            g2.drawRenderedImage(image, at);
        }

        private final Point p = new Point();

        @Override
        public void mouseClicked(MouseEvent e) {

        }

        @Override
        public void mousePressed(MouseEvent e) {
            p.setLocation(e.getPoint());
        }

        @Override
        public void mouseReleased(MouseEvent e) {
        }

        @Override
        public void mouseEntered(MouseEvent e) {

        }

        @Override
        public void mouseExited(MouseEvent e) {
        }

        @Override
        public void mouseDragged(MouseEvent e) {
            var deltaX = e.getX() - p.getX();
            var deltaY = e.getY() - p.getY();
            var newAt = AffineTransform.getTranslateInstance(deltaX, deltaY);
            at.preConcatenate(newAt);
            p.setLocation(e.getPoint());
            repaint();
            RepaintManager.currentManager(this).markCompletelyDirty(this);
        }

        @Override
        public void mouseMoved(MouseEvent e) {
        }

        @Override
        public void mouseWheelMoved(MouseWheelEvent e) {
            var scale = e.getWheelRotation() < 0 ? 1.1 : 0.9;
            var mod = AffineTransform.getTranslateInstance(e.getX(), e.getY());
            mod.scale(scale, scale);
            mod.translate(-e.getX(), -e.getY());
            at.preConcatenate(mod);
            RepaintManager.currentManager(this).markCompletelyDirty(this);
        }
    }
}
