/* TODO:
- [ ] Contract deployment
- [ ] SAFE wallet transaction simulation
- [ ] Testnet support
- [ ] End-to-end test including proof verification
*/

pub mod simulator;
pub mod db;
pub mod erc20;

#[cfg(test)]
pub mod tests;
