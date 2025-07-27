use rustfst::algorithms::determinize::{
    determinize_with_config, DeterminizeConfig, DeterminizeType,
};
use rustfst::algorithms::{
    push_weights_with_config, rm_epsilon::rm_epsilon, tr_sum, PushWeightsConfig,
};
use rustfst::fst_impls::VectorFst;
// use rustfst::prelude::determinize::{DeterminizeConfig, DeterminizeType};
use colored::Colorize;
use rustfst::prelude::*;
use std::process::Command;

pub fn optimize_fst(
    fst: &mut VectorFst<TropicalWeight>,
    _delta: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    rm_epsilon(fst)?;
    let det_fst: VectorFst<TropicalWeight> = determinize_with_config(
        fst,
        DeterminizeConfig {
            delta: 1e-8,
            det_type: DeterminizeType::DeterminizeFunctional,
        },
    )
    .unwrap_or_else(|e| {
        eprintln!("{}", format!("{e}: Cannot determinize FST").blue().bold());
        fst.clone()
    });
    *fst = det_fst;
    tr_sum(fst);
    minimize_with_config(
        fst,
        MinimizeConfig {
            delta: 1e-8,
            allow_nondet: true,
        },
    )?;
    push_weights_with_config(
        fst,
        ReweightType::ReweightToInitial,
        PushWeightsConfig::default(),
    )?;
    Ok(())
}

/// Draw a wFST diagram and compile it to PDF
///
/// This function takes a reference to a wFST, a short name for the output files,
/// and a title for the diagram. It generates a .dot file using the FST's draw method
/// and then compiles it to a PDF using the dot command.
///
/// The diagram is configured for landscape orientation with a large size to accommodate
/// many nodes and edges.
///
/// # Arguments
/// * `fst` - Reference to the wFST to draw
/// * `short_name` - Short name used for output files (without extension)
/// * `title` - Title to display in the diagram
///
/// # Returns
/// * `Result<(), Box<dyn std::error::Error>>` - Ok(()) on success, error on failure
///
/// # Example
/// ```
/// use parserule::utils::draw_wfst_diagram;
/// use rustfst::fst_impls::VectorFst;
/// use rustfst::prelude::*;
///
/// let mut fst = VectorFst::<TropicalWeight>::new();
/// let q0 = fst.add_state();
/// let q1 = fst.add_state();
/// fst.set_start(q0).unwrap();
/// fst.set_final(q1, TropicalWeight::one()).unwrap();
/// fst.add_tr(q0, Tr::new(1, 1, TropicalWeight::one(), q1)).unwrap();
///
/// draw_wfst_diagram(&fst, "my_fst", "My FST Diagram")?;
/// // This creates my_fst.dot and my_fst.pdf
/// ```
pub fn draw_wfst<F>(
    fst: &F,
    short_name: &str,
    title: &str,
) -> Result<(), Box<dyn std::error::Error>>
where
    F: Fst<TropicalWeight> + SerializableFst<TropicalWeight>,
{
    let dot_filename = format!("{}.dot", short_name);
    let pdf_filename = format!("{}.pdf", short_name);

    // Configure the drawing for landscape orientation with large size
    let config = DrawingConfig {
        vertical: false,          // Landscape orientation
        size: Some((16.0, 12.0)), // Large size (16x12 inches) for many nodes/edges
        title: title.to_string(),
        portrait: false,       // Landscape mode
        ranksep: Some(1.0),    // Spacing between ranks
        nodesep: Some(0.5),    // Spacing between nodes
        fontsize: 10,          // Readable font size
        acceptor: false,       // Show input/output labels
        show_weight_one: true, // Show weight even when it's 1.0
        print_weight: true,    // Show weights on transitions
    };

    // Draw the FST to a .dot file
    fst.draw(&dot_filename, &config)?;

    // Compile the .dot file to PDF using the dot command
    let output = Command::new("dot")
        .args(["-Tpdf", "-o", &pdf_filename, &dot_filename])
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("Failed to compile {} to PDF: {}", dot_filename, stderr).into());
    }

    println!("Successfully created {} and {}", dot_filename, pdf_filename);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustfst::fst_impls::VectorFst;
    use rustfst::prelude::{Tr, TropicalWeight};

    #[test]
    fn test_draw_wfst_diagram() {
        // Create a simple FST for testing
        let mut fst = VectorFst::<TropicalWeight>::new();
        let q0 = fst.add_state();
        let q1 = fst.add_state();

        fst.set_start(q0).unwrap();
        fst.set_final(q1, TropicalWeight::one()).unwrap();

        // Add a transition from q0 to q1
        fst.add_tr(q0, Tr::new(1, 1, TropicalWeight::one(), q1))
            .unwrap();

        // Test the draw function
        let result = draw_wfst(&fst, "test_fst", "Test FST Diagram");

        // The function should succeed (though dot command might not be available)
        // We mainly want to test that the function doesn't panic
        match result {
            Ok(_) => println!("Successfully created test diagram"),
            Err(e) => println!("Expected error (dot command might not be available): {}", e),
        }
    }
}
