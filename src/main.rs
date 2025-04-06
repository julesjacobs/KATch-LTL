use clap::Parser;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

mod aut;
mod expr;
mod parser;
#[allow(unused, non_snake_case)]
mod pre;
mod sp;
mod spp;

/// A simple parser for K2 expressions, operating on files or directories.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// The file or directory path to parse
    path: PathBuf,

    /// Number of fields (k) for the parser
    #[arg(short, long, default_value_t = 4)]
    k: u32,
}

fn main() {
    let cli = Cli::parse();
    let path = cli.path;
    let num_fields = cli.k;

    if !path.exists() {
        eprintln!("Error: Path \"{}\" does not exist.", path.display());
        std::process::exit(1);
    }

    if path.is_dir() {
        process_directory(&path, num_fields);
    } else if path.is_file() {
        process_file(&path, num_fields);
    } else {
        eprintln!("Error: Path \"{}\" is neither a file nor a directory.", path.display());
        std::process::exit(1);
    }
}

fn process_directory(dir_path: &Path, num_fields: u32) {
    println!("Processing directory: {}", dir_path.display());
    let mut found_k2_files = false;
    for entry in WalkDir::new(dir_path).into_iter().filter_map(|e| e.ok()) {
        let path = entry.path();
        if path.is_file() {
            if let Some(ext) = path.extension() {
                if ext == "k2" {
                    found_k2_files = true;
                    process_file(path, num_fields);
                }
            }
        }
    }
    if !found_k2_files {
        println!("No .k2 files found in directory.");
    }
}

fn process_file(file_path: &Path, num_fields: u32) {
    println!("--- Processing file: {} ---", file_path.display());
    match fs::read_to_string(file_path) {
        Ok(content) => {
            match parser::parse_expressions(&content, num_fields) {
                Ok(expressions) => {
                    if expressions.is_empty() {
                        println!("No expressions found or parsed.");
                    } else {
                        println!("Parsed Expressions:");
                        for (i, expr) in expressions.iter().enumerate() {
                            println!("  {}: {:?}", i + 1, expr);
                            // Potentially print a more user-friendly format later
                            // println!("  {}: {}", i + 1, expr);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("  Error parsing file: {}", e);
                }
            }
        }
        Err(e) => {
            eprintln!("  Error reading file: {}", e);
        }
    }
    println!("-------------------------------");
}
