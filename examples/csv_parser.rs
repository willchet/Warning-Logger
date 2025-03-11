#![feature(iter_intersperse)]

use anyhow::{Context, Result, anyhow};
use std::fs::File;
use std::io::BufRead;
use warning_logger::*;

#[derive(Debug)]
struct Record {
    id: u32,
    name: String,
    age: u8,
    lucky_numbers: Vec<u8>,
}

impl std::fmt::Display for Record {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Record {
            id,
            name,
            age,
            lucky_numbers,
        } = self;
        write!(
            f,
            "ID: {id:<3}Name: {name:<15}Age: {age:<5}Lucky Numbers: {}",
            lucky_numbers
                .iter()
                .map(|x| x.to_string())
                .intersperse(",".to_string())
                .collect::<String>()
        )
    }
}

fn parse_csv(file_path: &str) -> Result<Logger<Vec<Record>>> {
    let logger = BasicLogger::new(());

    let file = File::open(file_path).err_with_context(context!(
        "While opening {file_path}, the following error occurred:"
    ))?;

    let records = std::io::BufReader::new(file)
        .lines()
        .log_errors_with_context(
            &logger,
            context!("The following error occurred while reading a line of {file_path}:"),
        )
        .enumerate()
        .map(|(i, line)| {
            parse_line(line)
                .err_with_context(context!(
                    "Could not parse line {i} of {file_path} due to the error:"
                ))
                .warnings_with_context(context!(
                    "The following warnings occurred when parsing line {i} of {file_path}:"
                ))
        })
        .log_errors(&logger)
        .log_warnings(&logger)
        .collect::<Vec<_>>();

    Ok(records.wrap_with_warnings(logger))
}

fn parse_line(line: String) -> Result<Logger<Record>> {
    let logger = BasicLogger::new(());

    let mut line_parts = line.split(',');

    let id_field = line_parts
        .next()
        .with_context(context!("The ID field was missing"))?;
    let id = id_field
        .parse::<u32>()
        .err_with_context(context!("The following ID could not be parsed: {id_field}"))?;

    let name_field = line_parts
        .next()
        .with_context(context!("The name field was missing"))?
        .trim();
    if name_field.is_empty() {
        logger.log("The name field was empty");
    }
    let name = name_field.to_string();

    let age_field = line_parts
        .next()
        .with_context(context!("The age field was missing"))?
        .trim();
    let age = age_field.parse::<u8>().err_with_context(context!(
        "The following age could not be parsed: {age_field}"
    ))?;
    if !(18..100).contains(&age) {
        logger.log(format!("The age {age} was not not in 18-99"));
    }

    let lucky_numbers = parse_lucky_numbers(line_parts)
        .relog_with_context(
            context!("While parsing the lucky numbers, the following warnings occurred:"),
            &logger,
        )
        .err_with_context(context!(
            "Failed to parse the lucky numbers due to the following error:"
        ))?;

    let record = Record {
        id,
        name,
        age,
        lucky_numbers,
    };

    Ok(record.wrap_with_warnings(logger))
}

fn parse_lucky_numbers<'a>(iter: impl Iterator<Item = &'a str>) -> Logger<Result<Vec<u8>>> {
    let logger = BasicLogger::new(());
    let nums = iter
        .map(|x| x.parse::<u8>())
        .log_errors(&logger)
        .collect::<Vec<_>>();
    if nums.is_empty() {
        Err(anyhow!("No lucky numbers were parsed")).wrap_with_warnings(logger)
    } else {
        Ok(nums).wrap_with_warnings(logger)
    }
}

fn main() -> Result<()> {
    let records = parse_csv("examples/data.csv")?.print_warnings();

    println!();

    for record in records {
        println!("{record}");
    }

    Ok(())
}
