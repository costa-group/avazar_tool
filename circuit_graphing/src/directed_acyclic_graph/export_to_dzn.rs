use std::collections::{HashSet, BTreeSet};
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

pub fn write_dzn<P: AsRef<Path>>(
    path: P,
    adjacency: &[Vec<usize>],
    edges: &[(usize, usize)],
    fuzzy: &[bool],
    init_direction: &[usize],
    s_input: &HashSet<usize>,
    s_output: &HashSet<usize>,
) -> std::io::Result<()> {
    let n = adjacency.len();
    let m = edges.len();

    // Build incidence lists.
    let mut incidence: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
    for (idx, &(u, v)) in edges.iter().enumerate() {
        incidence[u].insert(idx+1);
        incidence[v].insert(idx+1);
    }

    let mut writer = BufWriter::new(File::create(path)?);

    writeln!(writer, "n = {};", n)?;
    writeln!(writer, "m = {};", m)?;
    writeln!(writer)?;

    // edges
    writeln!(writer, "edges = [| {}, {}", edges[0].0+1, edges[0].1+1)?;
    for &(u, v) in edges.iter().skip(1) {
        writeln!(writer, " | {}, {}", u+1, v+1)?;
    }
    writeln!(writer, "|];")?;
    writeln!(writer)?;

    writeln!(writer, "fuzzy = [")?;
    for (idx, val) in fuzzy.into_iter().enumerate() {
        if idx != 0 {write!(writer, ",")?;}
        write!(writer, "{}", val)?;
    }
    writeln!(writer, "];")?;
    writeln!(writer)?;

    writeln!(writer, "init_direction = [")?;
    for (idx, val) in init_direction.into_iter().enumerate() {
        if idx != 0 {write!(writer, ",")?;}
        write!(writer, "{}", val)?;
    }
    writeln!(writer, "];")?;
    writeln!(writer)?;

    // incidence
    writeln!(writer, "incidence = [")?;
    for set in &incidence {
        write_set(&mut writer, set)?;
    }
    writeln!(writer, "];")?;
    writeln!(writer)?;

    // adjacency
    writeln!(writer, "adjacency = [")?;
    for neighbors in adjacency {
        let set: BTreeSet<_> = neighbors.iter().copied().map(|x| x+1 ).collect();
        write_set(&mut writer, &set)?;
    }
    writeln!(writer, "];")?;

    // input/output sets
    write!(writer, "s_input = ")?;
    write_hashset(&mut writer, s_input)?;
    writeln!(writer, ";")?;

    write!(writer, "s_output = ")?;
    write_hashset(&mut writer, s_output)?;
    writeln!(writer, ";")?;

    Ok(())
}

fn write_set<W: Write>(
    writer: &mut W,
    set: &BTreeSet<usize>,
) -> std::io::Result<()> {
    write!(writer, "  {{")?;

    let mut first = true;
    for x in set {
        if !first {
            write!(writer, ",")?;
        }
        write!(writer, "{}", x)?;
        first = false;
    }

    writeln!(writer, "}},")?;
    Ok(())
}

fn write_hashset<W: Write>(
    writer: &mut W,
    set: &HashSet<usize>,
) -> std::io::Result<()> {
    let sorted: BTreeSet<_> = set.iter().copied().collect();

    write!(writer, "{{")?;
    let mut first = true;
    for x in sorted {
        if !first {
            write!(writer, ",")?;
        }
        write!(writer, "{}", x+1)?;
        first = false;
    }
    write!(writer, "}}")?;

    Ok(())
}