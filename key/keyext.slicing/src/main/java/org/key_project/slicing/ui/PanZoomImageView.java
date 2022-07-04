package org.key_project.slicing.ui;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.event.MouseWheelEvent;
import java.awt.event.MouseWheelListener;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;

/**
 * A simple image view that may be panned and zoomed by the user.
 *
 * TODO: move to key.ui? it can be used for any image
 *
 * @author Arne Keller
 */
public class PanZoomImageView extends JComponent
        implements MouseListener, MouseMotionListener, MouseWheelListener {
    /**
     * Image to be displayed.
     */
    private final transient BufferedImage image;
    /**
     * Current display transformation.
     */
    private final AffineTransform at;
    /**
     * Timer used to control redraws.
     */
    private Timer timer;
    /**
     * Time of last paint in milliseconds.
     */
    private long lastPaint = 0;
    /**
     * Whether to render the image using a fast interpolation method.
     */
    private boolean quickRender = false;
    /**
     * Variable used to record mouse movements.
     *
     * @see #mouseDragged(MouseEvent)
     */
    private final Point p = new Point();

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

        this.timer = new Timer(150, e -> {
            if (quickRender && System.currentTimeMillis() - lastPaint > 100) {
                quickRender = false;
                repaint();
                this.timer.stop();
            }
        });
        addComponentListener(new ResizeListener());
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);

        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION, quickRender ? RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR : RenderingHints.VALUE_INTERPOLATION_BICUBIC);
        g2.drawRenderedImage(image, at);
    }

    @Override
    public void mouseClicked(MouseEvent e) { }

    @Override
    public void mousePressed(MouseEvent e) {
        p.setLocation(e.getPoint());
    }

    @Override
    public void mouseReleased(MouseEvent e) { }

    @Override
    public void mouseEntered(MouseEvent e) { }

    @Override
    public void mouseExited(MouseEvent e) { }

    @Override
    public void mouseDragged(MouseEvent e) {
        var deltaX = e.getX() - p.getX();
        var deltaY = e.getY() - p.getY();
        moveBy(deltaX, deltaY, e.getPoint());
    }

    @Override
    public void mouseMoved(MouseEvent e) { }

    @Override
    public void mouseWheelMoved(MouseWheelEvent e) {
        var scale = e.getWheelRotation() < 0 ? 1.1 : 0.9;
        this.scale(scale, -e.getX(), -e.getY());
    }

    private void scale(double scale, double dx, double dy) {
        var mod = AffineTransform.getTranslateInstance(-dx, -dy);
        mod.scale(scale, scale);
        mod.translate(dx, dy);
        at.preConcatenate(mod);
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }

    private void moveBy(double dx, double dy, Point point) {
        var newAt = AffineTransform.getTranslateInstance(dx, dy);
        at.preConcatenate(newAt);
        p.setLocation(point);
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }

    private static class ResizeListener extends ComponentAdapter {
        private double prevWidth = 0;
        private double prevHeight = 0;
        private int events = 0;

        @Override
        public void componentResized(ComponentEvent e) {
            var pziw = (PanZoomImageView) e.getComponent();
            double newWidth = e.getComponent().getWidth();
            double newHeight = e.getComponent().getHeight();
            events++;
            if (events >= 3) {
                var ratio1 = newWidth / prevWidth;
                var ratio2 = newHeight / prevHeight;
                var ratio = 1.0;
                if (ratio1 > 1.0 && ratio2 > 1.0) {
                    ratio = Math.min(ratio1, ratio2);
                } else {
                    ratio = Math.max(ratio1, ratio2);
                }
                pziw.moveBy((newWidth - prevWidth) / 2.0, (newHeight - prevHeight) / 2.0, pziw.p);
                pziw.scale(ratio, -newWidth / 2.0, -newHeight / 2.0);
            }
                prevWidth = newWidth;
                prevHeight = newHeight;
        }
    }
}
