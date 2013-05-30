package warwick.marsh.util;

import java.awt.*;
import java.awt.event.*;
import javax.swing.border.*;

public class General {

    // Colour constants
    public static final Color DEFAULT_COLOUR    = new Color(220, 220, 255);
    public static final Color ERROR_COLOUR      = new Color(255, 0,   0  );
    public static final Color WARNING_COLOUR    = new Color(255, 100, 0  );

    // Font
    public static final Font DEFAULT_FONT = new Font("Dialog", Font.BOLD, 12);

    /** Method for adding components to Containers with GridBagLayouts
     * @param cont  the container to add the component to
     * @param comp  the component to add
     * @param gridx the x position, counting from 0 at the left
     * @param gridy the y position counting from 0 at the top
     * @param gridwidth  the number of cells to cover in x
     * @param gridheight the number of cells to cover in y
     * @param fill   what to do when the display area is larger than the component. See GribBagConstraints for more info
     * @param anchor where to position when the display area is larger than the component. See GribBagConstraints for more info
     */
    
    public static void addComponent (Container cont, Component comp, int gridx, int gridy, int gridwidth, int gridheight, int fill, int anchor){
	
	GridBagConstraints gbc = new GridBagConstraints ();
	gbc.gridx      = gridx;
	gbc.gridy      = gridy;
	gbc.gridwidth  = gridwidth;
	gbc.gridheight = gridheight;
	gbc.fill       = fill;
	gbc.anchor     = anchor;
	GridBagLayout gbLayout = (GridBagLayout)cont.getLayout();
	gbLayout.setConstraints(comp, gbc);
	cont.add (comp);
    }

    /** Method for adding components to Containers with GridBagLayouts as a load of equal action buttons
     * @param cont  the container to add the component to
     * @param comp  the component to add
     * @param gridx the x position, counting from 0 at the left
     * @param gridy the y position counting from 0 at the top
     */

    public static void addActionComponent (Container cont, Component comp, int gridx, int gridy){

	GridBagConstraints gbc = new GridBagConstraints ();
	gbc.gridx      = gridx;
	gbc.gridy      = gridy;
	gbc.gridwidth  = 1;
	gbc.gridheight = 1;
	gbc.insets     = new Insets(0,5,0,5);
	gbc.fill       = GridBagConstraints.HORIZONTAL;
	gbc.anchor     = GridBagConstraints.CENTER;
	GridBagLayout gbLayout = (GridBagLayout)cont.getLayout();
	gbLayout.setConstraints(comp, gbc);
	cont.add (comp);
    }
}

